int main1(int y,int f){
  int zvu, c, a, s, b4;
  zvu=82;
  c=zvu;
  a=0;
  s=-2;
  b4=c;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= a <= zvu;
  loop invariant (a > 0) ==> (s == zvu - a);
  loop invariant b4 == (a + 1) * c;
  loop invariant ((a == 0 && s == -2) || (s == zvu - a));
  loop invariant b4 == c * (a + 1);
  loop invariant s <= zvu - a;
  loop invariant c == zvu;
  loop assigns a, b4, s;
*/
while (a<=zvu-1) {
      a++;
      b4 = b4 + c;
      s = zvu-a;
  }
}