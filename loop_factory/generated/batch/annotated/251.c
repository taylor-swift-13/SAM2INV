int main1(int b,int q){
  int h, u, p;

  h=b;
  u=1;
  p=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p >= u;
  loop invariant p >= 1;
  loop invariant u >= 1;
  loop invariant h == b;
  loop invariant (h >= 1) ==> u <= h;
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant h == \at(b, Pre);
  loop invariant p >= 1 && (p == 1 || p % 4 == 0);
  loop invariant u >= 1 && (u == 1 || u % 3 == 0);
  loop invariant (p == 1) <==> (u == 1);
  loop assigns p, u;
*/
while (u<=h/3) {
      p = p*2;
      p = p*p;
      u = u*3;
  }

}
