int main1(int k,int p){
  int f, j, m, i;

  f=p+8;
  j=3;
  m=0;
  i=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m >= 0 && (f < 0 || m <= f) && i <= \at(p, Pre) + 2*m && i >= \at(p, Pre);
  loop invariant (i - \at(p, Pre)) % 2 == 0 && f == \at(p, Pre) + 8 && k == \at(k, Pre);

  loop invariant p == \at(p, Pre) && f == \at(p, Pre) + 8;
  loop invariant (m <= f/2) ==> i == \at(p, Pre);

  loop invariant f == \at(p, Pre) + 8 && p == \at(p, Pre) && k == \at(k, Pre) && m >= 0 && (f <= 0 || m <= f);
  loop invariant i >= \at(p, Pre) && i <= \at(p, Pre) + 2*m && ((i - \at(p, Pre)) % 2) == 0;

  loop invariant i >= \at(p, Pre) && i <= \at(p, Pre) + 2*m;


  loop invariant f == \at(p, Pre) + 8;
  loop invariant p == \at(p, Pre);
  loop invariant (m < f/2) ==> i == \at(p, Pre);

  loop invariant m >= 0;
  loop invariant (m == 0 || m <= f);
  loop invariant i >= \at(p, Pre);
  loop invariant i - 2*m <= \at(p, Pre);
  loop invariant p == \at(p, Pre) && k == \at(k, Pre);
  loop assigns i, m;
*/
while (m<f) {
      if (m>=f/2) {
          i = i+2;
      }
      m = m+1;
  }
/*@
  assert !(m<f) &&
         (m >= 0 && (f < 0 || m <= f) && i <= \at(p, Pre) + 2*m && i >= \at(p, Pre));
*/


}
