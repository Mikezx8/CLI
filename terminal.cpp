#include <QApplication>
#include <QWidget>
#include <QVBoxLayout>
#include <QScrollArea>
#include <QScrollBar>
#include <QKeyEvent>
#include <QMouseEvent>
#include <QContextMenuEvent>
#include <QMenu>
#include <QAction>
#include <QClipboard>
#include <QFontMetrics>
#include <QPainter>
#include <QTimer>
#include <QSocketNotifier>
#include <QColor>
#include <QScreen>
#include <QFile>
#include <QJsonDocument>
#include <QJsonObject>
#include <QDir>
#include <QPropertyAnimation>
#include <QGraphicsOpacityEffect>
#include <QSlider>
#include <QCheckBox>
#include <QLabel>
#include <QHBoxLayout>
#include <QLinearGradient>
#include <QRegularExpression>
#include <QPainterPath>

#include <cmath>

#include <pty.h>
#include <unistd.h>
#include <termios.h>
#include <sys/ioctl.h>
#include <sys/wait.h>
#include <signal.h>
#include <fcntl.h>
#include <string.h>

// ── ANSI colour tables ────────────────────────────────────────────────────────
static const QColor ansi16[16] = {
    {  12, 12, 12},{197, 15, 31},{19,161, 14},{193,156, 0},
    {  0,55,218},{136, 23,152},{58,150,221},{204,204,204},
    {118,118,118},{231, 72, 86},{22,198, 12},{249,241,165},
    { 59,120,255},{180,  0,158},{97,214,214},{242,242,242}
};
static QColor ansiColor(int n){
    if(n<16)  return ansi16[n];
    if(n<232){
        n-=16;
        int b=n%6, g=(n/6)%6, r=n/36;
        auto c=[](int v){return v?55+v*40:0;};
        return {c(r),c(g),c(b)};
    }
    int v=8+(n-232)*10;
    return {v,v,v};
}

// ── Cell ─────────────────────────────────────────────────────────────────────
struct Attr {
    QColor fg{204,204,204}, bg{0,0,0};
    bool bold=false, underline=false, italic=false, reverse=false;
};
struct Cell { QChar ch{' '}; Attr attr; };

// ── Screen buffer ─────────────────────────────────────────────────────────────
class Screen {
public:
    int cols, rows;
    int cx=0, cy=0;
    bool cursorVisible=true;
    QVector<QVector<Cell>> lines;
    QVector<QVector<Cell>> scrollback;
    Attr curAttr;
    bool wrapNext=false;

    // saved cursor
    int sx=0, sy=0;
    Attr sattr;

    // selection
    int selStartX=-1,selStartY=-1,selEndX=-1,selEndY=-1;

    Screen(int c,int r): cols(c),rows(r){
        lines.resize(r);
        for(auto &l:lines) l.resize(c);
    }

    void resize(int c,int r){
        cols=c; rows=r;
        lines.resize(r);
        for(auto &l:lines){
            l.resize(c);
        }
        cx=qMin(cx,c-1);
        cy=qMin(cy,r-1);
    }

    Cell &at(int x,int y){ return lines[y][x]; }

    void scrollUp(int top,int bot){
        if(top>=bot) return;
        scrollback.append(lines[top]);
        if(scrollback.size()>5000) scrollback.removeFirst();
        lines.removeAt(top);
        QVector<Cell> blank(cols);
        lines.insert(bot,blank);
    }

    void scrollDown(int top,int bot){
        lines.removeAt(bot);
        QVector<Cell> blank(cols);
        lines.insert(top,blank);
    }

    void clearLine(int y,int x1,int x2){
        for(int x=x1;x<=x2&&x<cols;x++)
            lines[y][x]={' ',curAttr};
    }

    void eraseLine(int y){ clearLine(y,0,cols-1); }

    // alternate screen buffer (for TUI apps like fastfetch, vim, etc.)
    QVector<QVector<Cell>> altLines;
    int altCx=0, altCy=0;
    Attr altAttr;
    bool altActive=false;

    void switchToAlt(){
        if(altActive) return;
        altActive=true;
        altLines=lines;
        altCx=cx; altCy=cy; altAttr=curAttr;
        // clear main screen for alt buffer
        lines.clear();
        lines.resize(rows);
        for(auto &l:lines) l.resize(cols);
        cx=0; cy=0; curAttr=Attr{};
    }

    void switchToNormal(){
        if(!altActive) return;
        altActive=false;
        lines=altLines;
        cx=altCx; cy=altCy; curAttr=altAttr;
        altLines.clear();
    }

    QString selectedText() const {
        if(selStartY<0) return {};
        int ay=selStartY,ax=selStartX,by=selEndY,bx=selEndX;
        if(ay>by||(ay==by&&ax>bx)){qSwap(ay,by);qSwap(ax,bx);}
        // map into scrollback+lines
        int sb=scrollback.size();
        QString out;
        for(int y=ay;y<=by;y++){
            int x0=(y==ay?ax:0), x1=(y==by?bx:cols-1);
            const QVector<Cell>*row=nullptr;
            if(y<sb) row=&scrollback[y];
            else if(y-sb<lines.size()) row=&lines[y-sb];
            if(!row) continue;
            for(int x=x0;x<=x1&&x<row->size();x++)
                out+=(*row)[x].ch;
            if(y<by) out+='\n';
        }
        return out.trimmed();
    }
};

// ── VT Parser ─────────────────────────────────────────────────────────────────
class VTParser : public QObject {
    Q_OBJECT
public:
    Screen *scr;
    int scrollTop=0, scrollBot;
    QByteArray buf;
    int master=-1;

    VTParser(Screen *s):scr(s),scrollBot(s->rows-1){}

    void feed(const QByteArray &data){
        buf+=data;
        parse();
    }

private:
    void parse(){
        int i=0;
        while(i<buf.size()){
            unsigned char c=buf[i];
            if(c==0x1b){
                if(i+1>=buf.size()) break;
                char next=buf[i+1];
                if(next=='['){
                    // CSI
                    int j=i+2;
                    while(j<buf.size()&&(buf[j]<0x40||buf[j]>0x7e)) j++;
                    if(j>=buf.size()) break;
                    QByteArray seq=buf.mid(i+2,j-(i+2));
                    char cmd=buf[j];
                    csi(seq,cmd);
                    i=j+1;
                } else if(next==']'){
                    // OSC — skip to BEL or ST
                    int j=i+2;
                    while(j<buf.size()&&buf[j]!=0x07&&
                          !(j+1<buf.size()&&buf[j]==0x1b&&buf[j+1]=='\\')) j++;
                    if(j>=buf.size()) break;
                    i=j+1;
                    if(i<buf.size()&&buf[i-1]==0x1b) i++;
                } else if(next=='('){
                    i+=3; // charset designation, skip
                } else {
                    esc(next); i+=2;
                }
            } else if(c=='\r'){
                scr->cx=0; i++;
            } else if(c=='\n'||c==0x0b||c==0x0c){
                linefeed(); i++;
            } else if(c=='\t'){
                scr->cx=((scr->cx/8)+1)*8;
                if(scr->cx>=scr->cols) scr->cx=scr->cols-1;
                i++;
            } else if(c==0x08){
                if(scr->cx>0) scr->cx--; i++;
            } else if(c==0x07){
                i++; // bell ignore
            } else if(c>=0x80){
                // UTF-8 multibyte
                int seqLen=0;
                if((c&0xE0)==0xC0) seqLen=2;
                else if((c&0xF0)==0xE0) seqLen=3;
                else if((c&0xF8)==0xF0) seqLen=4;
                else { i++; continue; }
                if(i+seqLen>buf.size()) break;
                QString s=QString::fromUtf8(buf.constData()+i,seqLen);
                // filter fish "no newline" marker U+23CE ⏎
                if(!s.isEmpty() && s[0].unicode() != 0x23CE) putChar(s[0]);
                i+=seqLen;
            } else if(c>=0x20){
                putChar(QChar(c)); i++;
            } else { i++; }
        }
        buf=buf.mid(i);
    }

    void linefeed(){
        scr->wrapNext=false;
        if(scr->cy==scrollBot) scr->scrollUp(scrollTop,scrollBot);
        else scr->cy=qMin(scr->cy+1,scr->rows-1);
    }

    void putChar(QChar ch){
        if(scr->wrapNext){
            scr->cx=0;
            linefeed();
            scr->wrapNext=false;
        }
        if(scr->cx<scr->cols&&scr->cy<scr->rows)
            scr->at(scr->cx,scr->cy)={ch,scr->curAttr};
        if(scr->cx+1>=scr->cols) scr->wrapNext=true;
        else scr->cx++;
    }

    QList<int> params(const QByteArray &seq){
        QList<int> p;
        for(auto &s:seq.split(';'))
            p.append(s.isEmpty()?0:s.toInt());
        if(p.isEmpty()) p.append(0);
        return p;
    }

    void csi(const QByteArray &seq, char cmd){
        auto p=params(seq);
        auto P=[&](int i,int def=0){return i<p.size()?p[i]:def;};
        switch(cmd){
        case 'A': scr->cy=qMax(0,scr->cy-qMax(1,P(0))); break;
        case 'B': scr->cy=qMin(scr->rows-1,scr->cy+qMax(1,P(0))); break;
        case 'C': scr->cx=qMin(scr->cols-1,scr->cx+qMax(1,P(0))); break;
        case 'D': scr->cx=qMax(0,scr->cx-qMax(1,P(0))); break;
        case 'E': scr->cy=qMin(scr->rows-1,scr->cy+qMax(1,P(0))); scr->cx=0; break;
        case 'F': scr->cy=qMax(0,scr->cy-qMax(1,P(0))); scr->cx=0; break;
        case 'G': scr->cx=qMax(0,qMin(scr->cols-1,P(0)-1)); break;
        case 'H': case 'f':
            scr->cy=qMax(0,qMin(scr->rows-1,P(0,1)-1));
            scr->cx=qMax(0,qMin(scr->cols-1,P(1,1)-1));
            break;
        case 'J':{
            int m=P(0);
            if(m==0){for(int y=scr->cy+1;y<scr->rows;y++)scr->eraseLine(y);scr->clearLine(scr->cy,scr->cx,scr->cols-1);}
            else if(m==1){for(int y=0;y<scr->cy;y++)scr->eraseLine(y);scr->clearLine(scr->cy,0,scr->cx);}
            else if(m==2){for(int y=0;y<scr->rows;y++)scr->eraseLine(y);}
            else if(m==3){scr->scrollback.clear();}  // erase scrollback
            break;}
        case 'K':{
            int m=P(0);
            if(m==0) scr->clearLine(scr->cy,scr->cx,scr->cols-1);
            else if(m==1) scr->clearLine(scr->cy,0,scr->cx);
            else if(m==2) scr->eraseLine(scr->cy);
            break;}
        case 'L':{ int n=qMax(1,P(0)); for(int i=0;i<n;i++) scr->scrollDown(scr->cy,scrollBot); break;}
        case 'M':{ int n=qMax(1,P(0)); for(int i=0;i<n;i++) scr->scrollUp(scr->cy,scrollBot); break;}
        case 'P':{ // delete chars
            int n=qMax(1,P(0));
            auto &l=scr->lines[scr->cy];
            l.remove(scr->cx,n);
            while(l.size()<scr->cols) l.append(Cell{});
            break;}
        case '@':{ // insert chars
            int n=qMax(1,P(0));
            for(int i=0;i<n;i++) scr->lines[scr->cy].insert(scr->cx,Cell{});
            while(scr->lines[scr->cy].size()>scr->cols) scr->lines[scr->cy].removeLast();
            break;}
        case 'S': for(int i=0;i<qMax(1,P(0));i++) scr->scrollUp(scrollTop,scrollBot); break;
        case 'T': for(int i=0;i<qMax(1,P(0));i++) scr->scrollDown(scrollTop,scrollBot); break;
        case 'r':
            scrollTop=qMax(0,P(0,1)-1);
            scrollBot=qMin(scr->rows-1,P(1,scr->rows)-1);
            break;
        case 'd': scr->cy=qMax(0,qMin(scr->rows-1,P(0,1)-1)); break;
        case 'm': sgr(p); break;
        case 's': scr->sx=scr->cx; scr->sy=scr->cy; scr->sattr=scr->curAttr; break;
        case 'u': scr->cx=scr->sx; scr->cy=scr->sy; scr->curAttr=scr->sattr; break;
        case 'h': case 'l':
            if(seq.startsWith('?')){
                int n=seq.mid(1).toInt();
                if(n==25) scr->cursorVisible=(cmd=='h');
                else if(n==1049||n==1047||n==47){
                    if(cmd=='h') scr->switchToAlt();
                    else          scr->switchToNormal();
                }
                // ?2004: bracketed paste — acknowledge but ignore
                // ?7: auto-wrap — ignore for now
            }
            break;
        case 'c': // Primary DA — respond as VT220
            if(master>=0) { const char *da="\x1b[?62;1;22c"; write(master,da,strlen(da)); }
            break;
        case 'n': // DSR
            if(P(0)==5&&master>=0) { const char *ok="\x1b[0n"; write(master,ok,strlen(ok)); }
            else if(P(0)==6&&master>=0) { QByteArray r; r="\x1b["+QByteArray::number(scr->cy+1)+";"+QByteArray::number(scr->cx+1)+"R"; write(master,r.constData(),r.size()); }
            break;
        default: break;
        }
        scr->wrapNext=false;
    }

    void esc(char c){
        switch(c){
        case '7': scr->sx=scr->cx;scr->sy=scr->cy;scr->sattr=scr->curAttr; break;
        case '8': scr->cx=scr->sx;scr->cy=scr->sy;scr->curAttr=scr->sattr; break;
        case 'M': // reverse index
            if(scr->cy==scrollTop) scr->scrollDown(scrollTop,scrollBot);
            else scr->cy=qMax(0,scr->cy-1);
            break;
        case 'c': // full reset
            for(auto &l:scr->lines) for(auto &c2:l) c2={};
            scr->cx=scr->cy=0; scr->curAttr=Attr{};
            scrollTop=0; scrollBot=scr->rows-1;
            break;
        default: break;
        }
    }

    void sgr(const QList<int>&p){
        Attr &a=scr->curAttr;
        for(int i=0;i<p.size();i++){
            int n=p[i];
            if(n==0){a=Attr{};}
            else if(n==1) a.bold=true;
            else if(n==3) a.italic=true;
            else if(n==4) a.underline=true;
            else if(n==7) a.reverse=true;
            else if(n==21||n==22) a.bold=false;
            else if(n==23) a.italic=false;
            else if(n==24) a.underline=false;
            else if(n==27) a.reverse=false;
            else if(n>=30&&n<=37) a.fg=ansi16[n-30];
            else if(n==38){
                if(i+2<p.size()&&p[i+1]==5){a.fg=ansiColor(p[i+2]);i+=2;}
                else if(i+4<p.size()&&p[i+1]==2){a.fg=QColor(p[i+2],p[i+3],p[i+4]);i+=4;}
            }
            else if(n==39) a.fg=QColor(204,204,204);
            else if(n>=40&&n<=47) a.bg=ansi16[n-40];
            else if(n==48){
                if(i+2<p.size()&&p[i+1]==5){a.bg=ansiColor(p[i+2]);i+=2;}
                else if(i+4<p.size()&&p[i+1]==2){a.bg=QColor(p[i+2],p[i+3],p[i+4]);i+=4;}
            }
            else if(n==49) a.bg=QColor(0,0,0);
            else if(n>=90&&n<=97) a.fg=ansi16[n-90+8];
            else if(n>=100&&n<=107) a.bg=ansi16[n-100+8];
        }
    }
};


// ── Theme ─────────────────────────────────────────────────────────────────────
struct Theme {
    QColor   highlight{255,144,83};
    QColor   bg1{0,0,0}, bg2;
    bool     gradient=false;
    double   angle=0;

    static Theme load(){
        Theme t;
        QString path = QDir::homePath()+"/.lumetask/theme.json";
        QFile f(path);
        if(!f.open(QIODevice::ReadOnly)) return t;
        QJsonObject obj = QJsonDocument::fromJson(f.readAll()).object();

        // highlight
        if(obj.contains("hightlight"))
            t.highlight = QColor(obj["hightlight"].toString());

        // bg-primary: plain color or "color1 color2 deg"
        if(obj.contains("bg-primary")){
            QString v = obj["bg-primary"].toString().trimmed();
            QRegularExpression re(R"(^(#\S+)\s+(#\S+)\s+([\d.]+)deg$)");
            auto m = re.match(v);
            if(m.hasMatch()){
                t.bg1      = QColor(m.captured(1));
                t.bg2      = QColor(m.captured(2));
                t.angle    = m.captured(3).toDouble();
                t.gradient = true;
            } else {
                t.bg1 = QColor(v);
            }
        }
        return t;
    }
};

// ── TermWidget ────────────────────────────────────────────────────────────────
class TermWidget : public QWidget {
    Q_OBJECT
private:
    Screen   *scr;
    VTParser *parser;
    QSocketNotifier *notifier;
    int master=-1;
    pid_t child=-1;

    QFont font;
    int cw, ch, baseline;

    // cursor blink
    QTimer *blinkTimer;
    bool blinkOn=true;

    // mouse selection
    bool selecting=false;
    QPoint selAnchor;

    // scroll offset into scrollback
    int scrollOffset=0;
    int padX=0, padY=0; // leftover pixels, distributed as padding

    // settings
    Theme   theme;
    bool    enhancedColors=false;
    bool    boldAll=false;
    double  bgOpacity=1.0;  // Controls the theme/gradient opacity
    QWidget *settingsPanel=nullptr;
    bool    panelOpen=false;

public:
    TermWidget(QWidget *parent=nullptr):QWidget(parent){
        setAttribute(Qt::WA_OpaquePaintEvent);
        setFocusPolicy(Qt::StrongFocus);
        setCursor(Qt::IBeamCursor);
        setSizePolicy(QSizePolicy::Expanding, QSizePolicy::Expanding);

        font=QFont("Monospace",11);
        font.setStyleHint(QFont::TypeWriter);
        QFontMetrics fm(font);
        cw=fm.horizontalAdvance('M');
        ch=fm.lineSpacing();
        baseline=fm.ascent();

        // initial size — will be corrected on first resizeEvent
        scr=new Screen(80,24);
        parser=new VTParser(scr);

        struct winsize ws{};
        ws.ws_col=scr->cols; ws.ws_row=scr->rows;

        child=forkpty(&master,nullptr,nullptr,&ws);
        if(child==0){
            setenv("TERM","xterm-256color",1);
            setenv("SHELL","/bin/bash",1);
            setenv("COLORTERM","truecolor",1);
            execlp("bash","bash",nullptr);
            _exit(1);
        }
        fcntl(master,F_SETFL,O_NONBLOCK);
        parser->master=master;

        notifier=new QSocketNotifier(master,QSocketNotifier::Read,this);
        connect(notifier,&QSocketNotifier::activated,this,&TermWidget::onData);

        blinkTimer=new QTimer(this);
        connect(blinkTimer,&QTimer::timeout,[this]{
            blinkOn=!blinkOn; update();
        });
        blinkTimer->start(500);

        // load theme
        theme=Theme::load();

        // build settings panel
        buildSettingsPanel();
    }

    ~TermWidget(){
        if(child>0) kill(child,SIGHUP);
    }

    QSize sizeHint() const override { return QSize(); }

private slots:
    void onData(){
        char buf[8192];
        ssize_t n=read(master,buf,sizeof(buf));
        if(n<=0) return;
        int sbBefore=scr->scrollback.size();
        parser->feed(QByteArray(buf,n));
        if(scrollOffset>0){
            int added=scr->scrollback.size()-sbBefore;
            if(added>0) scrollOffset=qMin(scrollOffset+added,(int)scr->scrollback.size());
        }
        update();
    }

protected:
    void paintEvent(QPaintEvent *) override {
        QPainter p(this);
        p.setFont(font);

        // Draw the theme background with opacity
        if(theme.gradient){
            double rad=theme.angle*M_PI/180.0;
            double cx2=width()/2.0, cy2=height()/2.0;
            double dx=cos(rad)*width()/2.0, dy=sin(rad)*height()/2.0;
            QLinearGradient grad(cx2-dx,cy2-dy,cx2+dx,cy2+dy);
            QColor bg1 = theme.bg1;
            QColor bg2 = theme.bg2;
            bg1.setAlphaF(bgOpacity);
            bg2.setAlphaF(bgOpacity);
            grad.setColorAt(0,bg1);
            grad.setColorAt(1,bg2);
            p.fillRect(rect(),grad);
        } else {
            QColor bg = theme.bg1;
            bg.setAlphaF(bgOpacity);
            p.fillRect(rect(),bg);
        }

        int sbSize=scr->scrollback.size();
        int totalRows=sbSize+scr->rows;
        int visRows=scr->rows;
        int firstRow=totalRows-scr->rows-scrollOffset;
        firstRow=qMax(0,firstRow);

        for(int row=0;row<visRows;row++){
            int srcRow=firstRow+row;
            const QVector<Cell>*line=nullptr;
            if(srcRow<sbSize) line=&scr->scrollback[srcRow];
            else if(srcRow-sbSize<scr->rows) line=&scr->lines[srcRow-sbSize];
            else break;

            int y=padY+row*ch;
            for(int col=0;col<scr->cols&&col<line->size();col++){
                const Cell &cell=(*line)[col];
                Attr a=cell.attr;

                QColor fg=a.bold&&a.fg==QColor(204,204,204)?Qt::white:a.fg;
                QColor bg=a.bg;
                
                // If background is black (0,0,0), make it transparent so theme shows through
                if(bg == QColor(0,0,0)) {
                    bg.setAlpha(0);
                }
                
                if(a.reverse) qSwap(fg,bg);

                bool inSel=false;
                if(scr->selStartY>=0){
                    int ay=scr->selStartY,ax=scr->selStartX;
                    int by=scr->selEndY,  bx=scr->selEndX;
                    if(ay>by||(ay==by&&ax>bx)){qSwap(ay,by);qSwap(ax,bx);}
                    int vy=srcRow,vx=col;
                    if(vy>ay||(vy==ay&&vx>=ax))
                        if(vy<by||(vy==by&&vx<=bx)) inSel=true;
                }
                if(inSel){ fg=Qt::black; bg=theme.highlight; }

                // enhanced colors: boost saturation
                if(enhancedColors&&!inSel){
                    auto boost=[](QColor c)->QColor{
                        int h,s,v,a; c.getHsv(&h,&s,&v,&a);
                        s=qMin(255,int(s*1.5)); v=qMin(255,int(v*1.1));
                        c.setHsv(h,s,v,a); return c;
                    };
                    fg=boost(fg);
                }
                // bold all
                if(boldAll) a.bold=true;

                int x=padX+col*cw;
                
                // Only draw background if it's not transparent
                if(bg.alpha() > 0) {
                    p.fillRect(x,y,cw,ch,bg);
                }
                
                if(!cell.ch.isSpace()){
                    p.setPen(fg);
                    if(a.bold){ QFont bf=font; bf.setBold(true); p.setFont(bf); }
                    if(a.italic){ QFont itf=p.font(); itf.setItalic(true); p.setFont(itf); }
                    p.drawText(x,y+baseline,cell.ch);
                    if(a.bold||a.italic) p.setFont(font);
                    if(a.underline) p.drawLine(x,y+baseline+1,x+cw,y+baseline+1);
                }
            }
        }

        // cursor
        if(scr->cursorVisible&&scrollOffset==0&&blinkOn){
            int cx=scr->cx, cy=scr->cy;
            int x=padX+cx*cw, y=padY+cy*ch;
            p.fillRect(x,y,cw,ch,QColor(220,220,220));
            const Cell &cc=scr->lines[cy][qMin(cx,scr->cols-1)];
            if(!cc.ch.isSpace()){
                p.setPen(Qt::black);
                p.drawText(x,y+baseline,cc.ch);
            }
        }
    }

    void resizeEvent(QResizeEvent *ev) override {
        QWidget::resizeEvent(ev);
        if(settingsPanel&&panelOpen){
            int pw=qMin(260,width());
            settingsPanel->setGeometry(width()-pw,0,pw,height());
        }
        int cols=qMax(1,width()/cw);
        int rows=qMax(1,height()/ch);
        padX=(width()  - cols*cw)/2;
        padY=(height() - rows*ch)/2;
        scr->resize(cols,rows);
        parser->scrollBot=rows-1;
        struct winsize ws{};
        ws.ws_col=cols; ws.ws_row=rows;
        ioctl(master,TIOCSWINSZ,&ws);
    }

    void updateFont(int ptSize){
        if(ptSize < 6 || ptSize > 72) return;
        font.setPointSize(ptSize);
        QFontMetrics fm(font);
        cw       = fm.horizontalAdvance('M');
        ch       = fm.lineSpacing();
        baseline = fm.ascent();
        int cols = qMax(1, width()  / cw);
        int rows = qMax(1, height() / ch);
        padX = (width()  - cols*cw) / 2;
        padY = (height() - rows*ch) / 2;
        scr->resize(cols, rows);
        parser->scrollBot = rows - 1;
        struct winsize ws{};
        ws.ws_col = cols;
        ws.ws_row = rows;
        ioctl(master, TIOCSWINSZ, &ws);
        update();
    }

public:
    void buildSettingsPanel(){
        settingsPanel = new QWidget(this, Qt::Popup);
        settingsPanel->setObjectName("settingsPanel");
        settingsPanel->setStyleSheet(
            "#settingsPanel{"
            "  background:rgba(20,20,20,230);"
            "  border-left:1px solid #333;"
            "  border-radius:8px;"
            "}"
            "QLabel{ color:#ccc; font-size:13px; }"
            "QCheckBox{ color:#ccc; font-size:13px; }"
            "QCheckBox::indicator{ width:16px;height:16px; }"
            "QSlider::groove:horizontal{ background:#333;height:4px;border-radius:2px; }"
            "QSlider::handle:horizontal{ background:#ff9053;width:14px;height:14px;margin:-5px 0;border-radius:7px; }"
            "QSlider::sub-page:horizontal{ background:#ff9053;border-radius:2px; }"
        );

        auto *vl = new QVBoxLayout(settingsPanel);
        vl->setContentsMargins(16,20,16,20);
        vl->setSpacing(18);

        auto *title = new QLabel("Settings", settingsPanel);
        title->setStyleSheet("color:#ff9053;font-size:15px;font-weight:bold;");
        vl->addWidget(title);

        // enhanced colors
        auto *cbEnhanced = new QCheckBox("Enhanced Colors", settingsPanel);
        cbEnhanced->setChecked(enhancedColors);
        connect(cbEnhanced, &QCheckBox::toggled, [this](bool v){ enhancedColors=v; update(); });
        vl->addWidget(cbEnhanced);

        // bold text
        auto *cbBold = new QCheckBox("Bold Text", settingsPanel);
        cbBold->setChecked(boldAll);
        connect(cbBold, &QCheckBox::toggled, [this](bool v){ boldAll=v; update(); });
        vl->addWidget(cbBold);

        // Background opacity - controls the theme/gradient opacity
        auto *lblOp = new QLabel("Background Opacity", settingsPanel);
        vl->addWidget(lblOp);
        auto *slOp = new QSlider(Qt::Horizontal, settingsPanel);
        slOp->setRange(0,100);
        slOp->setValue(int(bgOpacity*100));
        connect(slOp, &QSlider::valueChanged, [this](int v){
            bgOpacity = v/100.0;
            update();
        });
        vl->addWidget(slOp);

        vl->addStretch();

        auto *hint = new QLabel("F1 to close", settingsPanel);
        hint->setStyleSheet("color:#555;font-size:11px;");
        vl->addWidget(hint);

        settingsPanel->hide();
    }

    void toggleSettings(){
        if(!settingsPanel) return;
        if(!panelOpen){
            int panelW = qMin(260, width());
            int panelH = height();
            QPoint globalPos = mapToGlobal(QPoint(width() - panelW, 0));
            settingsPanel->setGeometry(globalPos.x(), globalPos.y(), panelW, panelH);
            settingsPanel->show();
            settingsPanel->raise();
            panelOpen = true;
        } else {
            settingsPanel->hide();
            panelOpen = false;
        }
    }

    void keyPressEvent(QKeyEvent *ke) override {
        QByteArray data;
        bool ctrl=ke->modifiers()&Qt::ControlModifier;
        bool shift=ke->modifiers()&Qt::ShiftModifier;

        if(ctrl&&shift){
            if(ke->key()==Qt::Key_C){
                QString sel=scr->selectedText();
                if(!sel.isEmpty()) QApplication::clipboard()->setText(sel);
                return;
            }
            if(ke->key()==Qt::Key_V){
                QString clip=QApplication::clipboard()->text();
                write(master,clip.toUtf8().constData(),clip.toUtf8().size());
                return;
            }
        }

        if(ke->key()==Qt::Key_F1){ toggleSettings(); return; }

        if(ctrl&&(ke->key()==Qt::Key_Equal||ke->key()==Qt::Key_Plus)){
            updateFont(font.pointSize()+1); return;
        }
        if(ctrl&&ke->key()==Qt::Key_Minus){
            updateFont(font.pointSize()-1); return;
        }
        if(ctrl&&ke->key()==Qt::Key_0){
            updateFont(11); return;
        }

        if(ctrl && !shift){
            int k=ke->key();
            if(k>=Qt::Key_A&&k<=Qt::Key_Z){
                data=QByteArray(1,char(k-Qt::Key_A+1));
            } else if(k==Qt::Key_BracketLeft)  data="\x1b";
            else if(k==Qt::Key_Backslash)       data="\x1c";
            else if(k==Qt::Key_BracketRight)    data="\x1d";
            else if(k==Qt::Key_Space)           data=QByteArray(1,char(0));
            else if(k==Qt::Key_Underscore)      data=QByteArray(1,char(31));
            if(!data.isEmpty()){ scrollOffset=0; write(master,data.constData(),data.size()); return; }
        }

        switch(ke->key()){
        case Qt::Key_Return:
        case Qt::Key_Enter:     data="\r"; break;
        case Qt::Key_Backspace: data="\x7f"; break;
        case Qt::Key_Tab:       data=shift?"\x1b[Z":"\t"; break;
        case Qt::Key_Up:        data="\x1b[A"; break;
        case Qt::Key_Down:      data="\x1b[B"; break;
        case Qt::Key_Right:     data="\x1b[C"; break;
        case Qt::Key_Left:      data="\x1b[D"; break;
        case Qt::Key_Home:      data="\x1b[H"; break;
        case Qt::Key_End:       data="\x1b[F"; break;
        case Qt::Key_PageUp:
            scrollOffset=qMin(scrollOffset+scr->rows/2,scr->scrollback.size());
            update(); return;
        case Qt::Key_PageDown:
            scrollOffset=qMax(0,scrollOffset-scr->rows/2);
            update(); return;
        case Qt::Key_Delete:    data="\x1b[3~"; break;
        case Qt::Key_Insert:    data="\x1b[2~"; break;
        case Qt::Key_F1:        data="\x1bOP"; break;
        case Qt::Key_F2:        data="\x1bOQ"; break;
        case Qt::Key_F3:        data="\x1bOR"; break;
        case Qt::Key_F4:        data="\x1bOS"; break;
        case Qt::Key_F5:        data="\x1b[15~"; break;
        case Qt::Key_F6:        data="\x1b[17~"; break;
        case Qt::Key_F7:        data="\x1b[18~"; break;
        case Qt::Key_F8:        data="\x1b[19~"; break;
        case Qt::Key_F9:        data="\x1b[20~"; break;
        case Qt::Key_F10:       data="\x1b[21~"; break;
        case Qt::Key_F11:       data="\x1b[23~"; break;
        case Qt::Key_F12:       data="\x1b[24~"; break;
        default:
            data=ke->text().toUtf8();
        }
        if(!data.isEmpty()){
            scrollOffset=0;
            write(master,data.constData(),data.size());
        }
    }

    void mousePressEvent(QMouseEvent *ev) override {
        setFocus();
        if(ev->button()==Qt::LeftButton){
            bool shift=ev->modifiers()&Qt::ShiftModifier;
            if(shift && scr->selStartY>=0){
                int sbSize=scr->scrollback.size();
                scr->selEndX=qMax(0,qMin(scr->cols-1,(ev->x()-padX)/cw));
                scr->selEndY=sbSize-scrollOffset+(ev->y()-padY)/ch;
                selecting=true;
                selAnchor=QPoint(scr->selStartX*cw,
                    (scr->selStartY-(sbSize-scrollOffset))*ch);
            } else {
                scr->selStartY=scr->selEndY=-1;
                selAnchor=ev->pos();
                selecting=false;
            }
            update();
        }
    }

    void mouseMoveEvent(QMouseEvent *ev) override {
        if(!(ev->buttons()&Qt::LeftButton)) return;
        if(!selecting){
            if((ev->pos()-selAnchor).manhattanLength()<4) return;
            selecting=true;
            scr->selStartX=(selAnchor.x()-padX)/cw;
            int sbSize0=scr->scrollback.size();
            scr->selStartY=sbSize0-scrollOffset+(selAnchor.y()-padY)/ch;
        }
        scr->selEndX=qMax(0,qMin(scr->cols-1,(ev->x()-padX)/cw));
        int sbSize=scr->scrollback.size();
        scr->selEndY=sbSize-scrollOffset+(ev->y()-padY)/ch;
        update();
    }

    void mouseReleaseEvent(QMouseEvent *ev) override {
        if(ev->button()==Qt::LeftButton) selecting=false;
        if(ev->button()==Qt::MiddleButton){
            QString clip=QApplication::clipboard()->text(QClipboard::Selection);
            if(clip.isEmpty()) clip=QApplication::clipboard()->text();
            write(master,clip.toUtf8().constData(),clip.toUtf8().size());
        }
        QString sel=scr->selectedText();
        if(!sel.isEmpty())
            QApplication::clipboard()->setText(sel,QClipboard::Selection);
    }

    void mouseDoubleClickEvent(QMouseEvent *ev) override {
        int col=ev->x()/cw;
        int sbSize=scr->scrollback.size();
        int row=sbSize-scrollOffset+ev->y()/ch;
        if(row<0||row>=sbSize+scr->rows) return;
        const QVector<Cell>*line=nullptr;
        if(row<sbSize) line=&scr->scrollback[row];
        else if(row-sbSize<scr->rows) line=&scr->lines[row-sbSize];
        if(!line) return;
        int x0=col,x1=col;
        auto isWord=[&](int x)->bool{
            if(x<0||x>=line->size()) return false;
            QChar c=(*line)[x].ch;
            return c.isLetterOrNumber()||c=='_'||c=='-'||c=='.'||c=='/';
        };
        while(isWord(x0-1)) x0--;
        while(isWord(x1+1)) x1++;
        scr->selStartX=x0; scr->selEndX=x1;
        scr->selStartY=scr->selEndY=row;
        QString sel=scr->selectedText();
        if(!sel.isEmpty()) QApplication::clipboard()->setText(sel,QClipboard::Selection);
        update();
    }

    void wheelEvent(QWheelEvent *ev) override {
        scrollOffset+=ev->angleDelta().y()>0?3:-3;
        scrollOffset=qMax(0,qMin(scrollOffset,(int)scr->scrollback.size()));
        update();
    }

    void contextMenuEvent(QContextMenuEvent *ev) override {
        QMenu menu(this);
        menu.addAction("Copy  Ctrl+Shift+C",[this]{
            QString sel=scr->selectedText();
            if(!sel.isEmpty()) QApplication::clipboard()->setText(sel);
        });
        menu.addAction("Paste  Ctrl+Shift+V",[this]{
            QString clip=QApplication::clipboard()->text();
            write(master,clip.toUtf8().constData(),clip.toUtf8().size());
        });
        menu.addSeparator();
        menu.addAction("Font +  Ctrl+Shift+=",[this]{ updateFont(font.pointSize()+1); });
        menu.addAction("Font -  Ctrl+Shift+-",[this]{ updateFont(font.pointSize()-1); });
        menu.exec(ev->globalPos());
    }
};

#include "terminal.moc"

int main(int argc,char *argv[]){
    QApplication app(argc,argv);
    app.setApplicationName("Terminal");

    QWidget win;
    win.setWindowTitle("Terminal");
    win.setStyleSheet("background:#000;");
    auto *layout=new QVBoxLayout(&win);
    layout->setContentsMargins(0,0,0,0);
    auto *term=new TermWidget(&win);
    layout->addWidget(term);
    win.show();
    return app.exec();
}