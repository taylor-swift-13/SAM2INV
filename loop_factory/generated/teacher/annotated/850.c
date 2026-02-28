int main1(int b,int k,int p){
  int t, v, a, i;

  t=(p%7)+4;
  v=0;
  a=0;
  i=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant t == (p % 7) + 4;


  loop invariant i <= a;
  loop invariant p == \at(p, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);

  loop invariant (a < t/2) ==> (i == a);
  loop invariant a >= 0;
  loop invariant -a <= i <= a;
  loop invariant 0 <= a <= t && -a <= i <= a && (a <= t/2) ==> i == a && (a > t/2) ==> i == t - a - (t % 2);

  loop assigns i, a;
*/
while (a<t) {
      if (a<t/2) {
          i = i+1;
      }
      else {
          i = i-1;
      }
      a = a+1;
  }

}
