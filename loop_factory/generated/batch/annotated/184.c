int main1(int b,int m){
  int a, i, v;

  a=m;
  i=a;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant i <= a;
  loop invariant (v == i) || (v == i + 2);
  loop invariant v <= a;
  loop invariant a == \at(m, Pre);
  loop invariant i % 2 == a % 2;
  loop invariant v == i || v == i + 2;

  loop invariant a == m;
  loop invariant v >= i;
  loop invariant i % 2 == v % 2;
  loop invariant v <= i + 2;
  loop assigns v, i;
*/
while (i>=2) {
      if (i+4<=v+a) {
          v = v+v;
      }
      else {
          v = v+i;
      }
      v = i;
      i = i-2;
  }

}
