int main1(){
  int j7, x4x, mjk, u, j;
  j7=1;
  x4x=0;
  mjk=(1%40)+2;
  u=0;
  j=x4x;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j7 == 1;
  loop invariant 0 <= u <= 3;
  loop invariant mjk + u <= 4;
  loop invariant (u == 0) ==> (mjk == 3);
  loop invariant j >= 0;
  loop invariant (mjk == 3 || mjk == 1);
  loop assigns u, mjk, j;
*/
while (mjk!=u) {
      u = mjk;
      mjk = (mjk+j7/mjk)/2;
      j = j+(mjk%6);
  }
}