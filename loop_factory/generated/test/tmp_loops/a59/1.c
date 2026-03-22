int main1(int c,int r){
  int j, lr, l, yk, ul, l1w, fg, du, f70;

  j=(r%34)+15;
  lr=0;
  l=(r%20)+10;
  yk=(r%15)+8;
  ul=j;
  l1w=c;
  fg=j;
  du=j;
  f70=lr;

  while (l>0&&yk>0) {
      if (!(!(lr%2==0))) {
          l--;
      }
      else {
          yk--;
      }
      lr = lr + 1;
      if (j*j<=j+3) {
          du = du*du+fg;
      }
      c = c+(lr%2);
      ul = ul+(yk%7);
      f70 = f70+(lr%2);
      r += 2;
      ul += lr;
      l1w = l1w*l1w;
      fg = fg+ul*l1w;
  }

}
