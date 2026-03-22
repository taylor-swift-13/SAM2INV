int main1(int u){
  int w, t25, atw, f, b;

  w=u;
  t25=0;
  atw=t25;
  f=t25;
  b=w;

  while (1) {
      if (!(t25 < w)) {
          break;
      }
      f = f*2+(f%2)+2;
      atw = atw+(b%4);
      t25 = t25 + 1;
  }

}
