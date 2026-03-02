int main1(int k,int q){
  int a, j, o, u;

  a=57;
  j=1;
  o=j;
  u=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ( (u == -5 && o == 1) || (o == u*u) );
  loop invariant (u >= -5);
  loop invariant (o >= 0);
  loop invariant o <= u*u;
  loop invariant -5 <= u;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant (o == u*u) || (u == -5 && o == 1);
  loop invariant k == \at(k,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant u >= -5;
  loop invariant o >= 0;
  loop invariant a == 57 && u >= -5 && o >= 0;
  loop invariant k == \at(k,Pre) && q == \at(q,Pre) && u >= -5;
  loop invariant o <= u*u && k == \at(k, Pre) && q == \at(q, Pre);
  loop invariant ((u == -5 && o == 1) || (o == u*u)) && u >= -5 && o >= 0;
  loop invariant (q == \at(q, Pre)) && (k == \at(k, Pre));
  loop assigns u, o;
*/
while (1) {
      u = u+1;
      o = u*u;
  }

}
