int main1(int p,int q){
  int c, h, v, r, s;

  c=q+15;
  h=3;
  v=0;
  r=-8;
  s=c;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == \at(q, Pre) + 15;
  loop invariant s == c;
  loop invariant q == \at(q, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (v == 0) || (v == 1 + 2 * c);
  loop invariant c == q + 15;
  loop invariant v == 0 || v == c + s + 1;
  loop invariant v == 0 || v == c + 1 + s;
  loop invariant (v == 0) || (v == 2*c + 1);
  loop invariant (v == 0) ==> (r == -8);
  loop assigns r, v;
*/
while (1) {
      r = c-v;
      v = v+1;
      v = v+r+s;
  }

}
