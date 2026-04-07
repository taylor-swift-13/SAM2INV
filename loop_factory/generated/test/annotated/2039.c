int main1(){
  int x1, rd, a, q0n, b63;
  x1=44;
  rd=0;
  a=x1;
  q0n=1;
  b63=rd;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= rd;
  loop invariant rd <= x1;
  loop invariant q0n == 1 + rd * (a % 9);
  loop invariant b63 >= 0;
  loop invariant a == 44;
  loop invariant x1 == 44;
  loop assigns rd, b63, q0n;
*/
while (rd < x1) {
      rd++;
      b63 = b63*2+(a%7)+2;
      q0n = q0n+(a%9);
      b63 = b63*b63+a;
  }
}