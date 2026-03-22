int main1(int t,int w){
  int uw, t6, olp, n30k, xe, cq, td, djzd;
  uw=w-9;
  t6=uw;
  olp=0;
  n30k=0;
  xe=uw;
  cq=0;
  td=10;
  djzd=uw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant djzd == uw;
  loop invariant t == \at(t,Pre) + 3*(olp/2);
  loop invariant (olp % 2 == 0);
  loop invariant td - 10 == n30k - (olp/2);
  loop invariant olp >= 0;
  loop invariant cq >= 0;
  loop invariant (olp == 0) ==> (xe == uw);
  loop invariant t6  == uw;
  loop invariant ((t6 % 4) != 0) ==> (w == \at(w,Pre));
  loop assigns olp, xe, w, td, t, n30k, cq, djzd;
*/
while (olp<uw) {
      olp += 2;
      if (cq<=xe) {
          xe = cq;
      }
      if ((t6%4)==0) {
          w += t6;
      }
      td = td + xe;
      t = t + 3;
      n30k = n30k + xe;
      cq = cq+olp-xe;
      djzd = djzd+xe-xe;
      n30k++;
      cq = cq - 1;
  }
}