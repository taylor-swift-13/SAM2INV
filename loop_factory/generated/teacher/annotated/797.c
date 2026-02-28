int main1(int a,int b){
  int n, i, v, o;

  n=a-7;
  i=0;
  v=6;
  o=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 6;
  loop invariant ((v - 6) % 4 == 0);
  loop invariant (v - 6) % 4 == 0;
  loop invariant o >= -5;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant n == a - 7;
  loop invariant v % 4 == 2;
  loop invariant (v % 4) == 2;

  loop invariant n == \at(a, Pre) - 7;
  loop assigns v, o;
*/
while (1) {
      v = v+3;
      o = o+3;
      v = v+1;
      o = o-1;
      if (v+7<n) {
          o = o+v;
      }
  }

}
