int main1(int k,int q){
  int h, c, v, n;

  h=k-2;
  c=h;
  v=q;
  n=c;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == k - 2;

  loop invariant h == \at(k, Pre) - 2;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant (v == \at(q, Pre) || (0 <= v && v <= 2));

  loop assigns v;
*/
while (v<h) {
      if (v<h) {
          v = v+1;
      }
      v = v*v+v;
      v = v%3;
  }

}
