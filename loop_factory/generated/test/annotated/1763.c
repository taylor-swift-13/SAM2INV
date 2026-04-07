int main1(int b){
  int e, jbeo, eve, bct;
  e=b;
  jbeo=0;
  eve=b+1;
  bct=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eve == (\at(b, Pre) + 1) + ((bct*(bct+1)/2) * (bct*(bct+1)/2));
  loop invariant 0 <= bct <= 1;
  loop invariant jbeo == 0;
  loop invariant eve == b + 1 + ((bct*(bct+1))/2) * ((bct*(bct+1))/2);
  loop invariant (bct == 0) ==> (e == b);
  loop invariant (bct > 0) ==> (e == 0);
  loop assigns bct, eve, e;
*/
while (jbeo+1<=e) {
      bct++;
      eve = eve+bct*bct*bct;
      e = (jbeo+1)-1;
  }
}