int main1(int w){
  int gd, n4t8, wqg, wt;
  gd=(w%8)+7;
  n4t8=gd;
  wqg=0;
  wt=gd;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == \at(w, Pre);
  loop invariant wqg + wt == gd;
  loop invariant n4t8 == gd;
  loop invariant wt >= 0;
  loop invariant wqg >= 0;
  loop assigns w, wqg, wt;
*/
while (wqg<gd&&wt>0) {
      wt -= 1;
      w = w+gd-n4t8;
      wqg = (1)+(wqg);
  }
}