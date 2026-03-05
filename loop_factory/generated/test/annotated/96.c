int main1(int m,int w){
  int f6, l6, vg, bc;
  f6=14;
  l6=0;
  vg=1;
  bc=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bc == 4 + 3*l6;
  loop invariant vg == 1 + 3*l6;
  loop invariant l6 <= f6;
  loop invariant f6 == 14;
  loop invariant m == \at(m, Pre);
  loop invariant w == \at(w, Pre);
  loop invariant 0 <= l6;
  loop assigns vg, bc, l6;
*/
while (l6<f6) {
      vg = vg + 3;
      bc = bc + 3;
      l6 = l6 + 1;
  }
}