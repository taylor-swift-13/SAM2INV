int main1(int m,int q){
  int t, l, v, f;

  t=m;
  l=t;
  v=-6;
  f=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == t;
  loop invariant t == m;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);

  loop invariant t == \at(m,Pre);
  loop invariant f == \at(q,Pre);
  loop invariant (v + 6) % 4 == 0;
  loop invariant f == q;
  loop invariant (l < t/2) ==> ((f + 3) != 0 ==> (v + 6) % (f + 3) == 0) && ((f + 3) == 0 ==> v == -6);
  loop invariant (l >= t/2) ==> ((v + 6) % 4 == 0);
  loop assigns v;
*/
while (l>=1) {
      if (l<t/2) {
          v = v+f;
      }
      else {
          v = v+1;
      }
      v = v+3;
  }

}
