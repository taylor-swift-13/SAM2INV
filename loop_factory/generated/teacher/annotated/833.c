int main1(int a,int k,int n){
  int c, t, v, i;

  c=(a%8)+14;
  t=0;
  v=c;
  i=c;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == c + t*(t+1)/2;
  loop invariant t <= c;
  loop invariant (t <= a + c - 3) ==> i == c;

  loop invariant a == \at(a, Pre);
  loop invariant 0 <= t <= c;
  loop invariant 0 <= i <= c;
  loop invariant (t <= a + c - 3) ==> (i == c);

  loop invariant i <= c;
  loop invariant t >= 0;
  loop invariant (t <= a + c - 4) ==> (i == c);
  loop invariant i >= 0;
  loop invariant c == (a % 8) + 14;
  loop invariant i >= c - t;
  loop assigns v, i, t;
*/
while (t<c) {
      v = v+1;
      i = i-1;
      if (t+4<=a+c) {
          i = i+1;
      }
      v = v+t;
      t = t+1;
  }

}
