int main1(){
  int un, ybd, u9h, ba, b;
  un=1;
  ybd=un;
  u9h=0;
  ba=un;
  b=ybd;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ba == 1 - u9h;
  loop invariant 0 <= u9h <= un;
  loop invariant b == 1 + u9h*ybd + (u9h*(u9h + 1))/2;
  loop invariant un == 1;
  loop invariant ybd == 1;
  loop assigns b, ba, u9h;
*/
while (u9h<un&&ba>0) {
      ba--;
      u9h += 1;
      b += u9h;
      b = (ybd)+(b);
  }
}