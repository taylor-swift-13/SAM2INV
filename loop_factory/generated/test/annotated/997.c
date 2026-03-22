int main1(int n,int w){
  int ar, uu, hp;
  ar=(w%21)+15;
  uu=0;
  hp=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uu % 5 == 0;
  loop invariant ar == (w % 21) + 15;
  loop invariant hp == n + 2*(uu/5);
  loop invariant 0 <= uu;
  loop assigns hp, uu;
*/
for (; uu<=ar-1; uu = uu + 5) {
      hp += 2;
  }
}