int main141(int k,int b,int j){
  int lm7q, gn, dzoj, cg3, xh, tm, ez;

  lm7q=k+10;
  gn=0;
  dzoj=(k%20)+5;
  cg3=(k%20)+5;
  xh=(k%20)+5;
  tm=lm7q;
  ez=0;

  while (dzoj>0) {
      if (cg3>0) {
          if (xh>0) {
              dzoj -= 1;
              cg3 -= 1;
              xh = xh - 1;
          }
      }
      ez += 2;
      k = k + gn;
      tm += 2;
  }

}
