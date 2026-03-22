int main1(int f,int y){
  int lg, h, s, ev;
  lg=42;
  h=0;
  s=0;
  ev=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h + ev == 4;
  loop invariant s == 4*h - h*(h-1)/2;
  loop invariant 0 <= h <= lg;
  loop invariant 0 <= ev;
  loop invariant f == \at(f, Pre) + s - h;
  loop assigns s, h, ev, f;
*/
while (h<lg&&ev>0) {
      s = s + ev;
      h += 1;
      ev--;
      f = f + ev;
  }
}