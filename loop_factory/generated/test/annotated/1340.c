int main1(int d){
  int rk, j, kwz;
  rk=0;
  j=(d%28)+10;
  kwz=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j + rk * (rk - 1) / 2 == ((\at(d,Pre) % 28) + 10);
  loop invariant kwz - rk * (rk + 1) / 2 == 8;
  loop invariant rk >= 0;
  loop invariant j + (rk*(rk - 1))/2 == (d % 28) + 10;
  loop assigns j, rk, kwz;
*/
while (j>rk) {
      j = j - rk;
      rk += 1;
      kwz = kwz + rk;
  }
}