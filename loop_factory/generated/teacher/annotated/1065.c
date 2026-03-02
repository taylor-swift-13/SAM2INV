int main1(int a,int q){
  int i, j, v;

  i=a-3;
  j=0;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant i == \at(a, Pre) - 3;
  loop invariant j == 0;
  loop invariant v >= \at(a, Pre) && ((v - \at(a, Pre)) % 4) == 0;
  loop invariant (v - \at(a, Pre)) % 4 == 0;
  loop invariant v >= \at(a, Pre);
  loop invariant (v - \at(a, Pre)) % 4 == 0 && v >= \at(a, Pre);
  loop invariant j == 0 && i == \at(a, Pre) - 3 && q == \at(q, Pre) && a == \at(a, Pre);
  loop invariant ((v - \at(a, Pre)) % 4) == 0;
  loop invariant i == a - 3 && j == 0 && v >= \at(a, Pre);
  loop invariant a == \at(a, Pre) && q == \at(q, Pre) && (v - \at(a, Pre)) % 4 == 0;
  loop invariant i == a - 3;
  loop invariant (v - a) % 4 == 0;
  loop invariant v >= a;
  loop invariant j == 0 && i == \at(a, Pre) - 3;
  loop invariant a == \at(a, Pre) && q == \at(q, Pre) && v >= \at(a, Pre) && (v - \at(a, Pre)) % 4 == 0;
  loop invariant a == \at(a, Pre) && q == \at(q, Pre) && i == \at(a, Pre) - 3 && j == 0;

  loop assigns v;
*/
while (1) {
      v = v+3;
      if ((j%2)==0) {
          v = v+1;
      }
  }

}
