int main1(int p,int q){
  int x, c, v;

  x=p;
  c=0;
  v=x;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c >= 0;
  loop invariant x == p;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant (c >= 1) ==> (v >= 0);
  loop invariant (p == 0) ==> (v == 0);
  loop invariant (c > 0) ==> (v >= 0);
  loop invariant (c == 0) ==> (v == x);
  loop assigns v, c;
*/
while (1) {
      v = v*v;
      c = c+1;
  }

}
