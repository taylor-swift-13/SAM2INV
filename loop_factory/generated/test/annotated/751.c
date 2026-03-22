int main1(){
  int y, okj, td, hq, fi, hj;
  y=0;
  okj=(1%60)+60;
  td=(1%9)+2;
  hq=0;
  fi=0;
  hj=y;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hj == hq * ((td * (td - 1)) / 2) + ((fi * (fi + 1)) / 2);
  loop invariant (td * hq) + fi <= okj;
  loop invariant 0 <= fi;
  loop invariant fi < td;
  loop invariant hj >= y;
  loop assigns fi, hq, hj;
*/
while (1) {
      if (okj<=td*hq+fi) {
          break;
      }
      if (fi==td-1) {
          fi = 0;
          hq++;
      }
      else {
          fi = fi + 1;
      }
      hj = (fi)+(hj);
  }
}