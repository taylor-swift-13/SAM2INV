int main1(int k,int q){
  int w, j, u;

  w=q;
  j=0;
  u=w;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == \at(q,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant k == \at(k,Pre);
  loop invariant w == q;
  loop invariant q == \at(q, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant (u == \at(q, Pre)) || ((u - 6) % 2 == 0);
  loop invariant (q % 2 == 0) ==> (u % 2 == 0);
  loop invariant w == \at(q, Pre);

  loop invariant q == \at(q, Pre) && k == \at(k, Pre);
  loop assigns u;
*/
while (1) {
      u = u+3;
      u = u*2;
  }

}
