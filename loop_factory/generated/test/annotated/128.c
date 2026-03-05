int main1(int g,int w){
  int ls, f3, g21y;
  ls=w;
  f3=ls;
  g21y=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ls == \at(w, Pre);
  loop invariant f3 >= \at(w, Pre);
  loop invariant f3 <= ls;
  loop invariant 0 <= g21y;
  loop invariant g21y <= 4;
  loop assigns g, f3, g21y;
*/
while (f3<ls) {
      g21y = f3%5;
      if (f3>=g21y) {
          g21y = (f3-g21y)%5;
          g21y = g21y+g21y-g21y;
      }
      else {
          g21y = g21y + g21y;
      }
      f3 = f3 + 1;
      g = g + g21y;
  }
}