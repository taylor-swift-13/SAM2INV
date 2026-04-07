int main1(int d){
  int ls, y53, sp, dlyf, l, r6, ux, r, mxgn, sz5;

  ls=68;
  y53=0;
  sp=0;
  dlyf=0;
  l=0;
  r6=0;
  ux=0;
  r=0;
  mxgn=ls;
  sz5=-8;

  while (y53<ls+(d%7)) {
      if (y53%11==0) {
          sp += 1;
          ux = ux + 1;
      }
      else {
          if (y53%8==0) {
              dlyf += 1;
              ux += 2;
          }
          else {
              if (y53%6==0) {
                  l = l + 1;
                  ux = ux + 3;
              }
              else {
                  if (1) {
                      r6 = r6 + 1;
                      ux += 4;
                  }
              }
          }
      }
      y53 = y53 + 1;
      mxgn = mxgn + sp;
      r = r+y53%8;
      mxgn = mxgn+sz5+sz5;
  }

}
