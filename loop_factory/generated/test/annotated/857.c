int main1(){
  int awj, wv, i, lp;
  awj=1+4;
  wv=0;
  i=wv;
  lp=wv;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == lp*lp;
  loop invariant wv <= awj;
  loop assigns lp, i, wv;
*/
while (wv<=awj-1) {
      lp++;
      i = lp*lp;
      wv = awj;
  }
}