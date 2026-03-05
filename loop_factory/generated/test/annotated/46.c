int main1(int s,int y){
  int uf, a;
  uf=(s%24)+19;
  a=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (a % 3) == 0;
  loop invariant a >= 0;
  loop invariant y == \at(y, Pre);
  loop invariant s == \at(s, Pre);
  loop invariant uf == (\at(s, Pre) % 24) + 19;
  loop invariant (a <= uf + 2) || (uf < 0);
  loop assigns a;
*/
while (a<uf) {
      a += 2;
      a++;
  }
}