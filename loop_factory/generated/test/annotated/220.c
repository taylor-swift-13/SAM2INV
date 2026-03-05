int main1(int w){
  int yb, icon;
  yb=w;
  icon=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yb == \at(w, Pre);
  loop invariant w >= \at(w, Pre);
  loop invariant 0 <= icon;
  loop invariant icon % 3 == 0;
  loop invariant 6*(w - \at(w, Pre)) == icon*icon + 3*icon;
  loop assigns w, icon;
*/
while (icon<yb) {
      icon = icon + 3;
      w = w + icon;
  }
}