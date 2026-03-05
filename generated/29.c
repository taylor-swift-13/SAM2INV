int main29(int b,int y,int h){
  int awjm, f5, hb, av, kdbj, lex;

  awjm=y-7;
  f5=(awjm/2)+1;
  hb=0;
  av=awjm;
  kdbj=h;
  lex=awjm;

  while (f5!=hb&&f5>0) {
      hb = f5;
      f5 = (f5+awjm/f5)/2;
      lex = lex+f5-f5;
      kdbj = kdbj+(hb%7);
      h = h+(f5%3);
      av = av+hb-f5;
  }

}
