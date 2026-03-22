int main1(int b,int t){
  int zew, q, k91, ma2;
  zew=34;
  q=1;
  k91=b;
  ma2=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k91 == \at(b, Pre);
  loop invariant ((q == 1 && ma2 == 0) || (q == zew && ma2 == k91));
  loop invariant k91 == b;
  loop invariant (q == 1) ==> (ma2 == 0);
  loop invariant (q == zew) ==> (ma2 == k91);
  loop invariant q <= zew;
  loop assigns ma2, q;
*/
while (q<zew) {
      ma2 = ma2+k91*q;
      q = zew;
  }
}