int main1(int p,int q){
  int l, i, v, e;

  l=q;
  i=0;
  v=-8;
  e=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 0;
  loop invariant l == q;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant e >= p;
  loop invariant l == \at(q, Pre);

  loop invariant (i < l/2) ==> 2*(v + 8) == (e - p) * ((e - p) + (2*p + 9));
  loop invariant i >= 0;

  loop assigns v, e;
*/
while (i<=l-4) {
      if (i<l/2) {
          v = v+e;
      }
      else {
          v = v+1;
      }
      v = v+5;
      e = e+1;
      e = e+i;
  }

}
