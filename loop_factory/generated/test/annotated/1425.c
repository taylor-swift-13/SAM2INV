int main1(){
  int fo8, dw, ny;
  fo8=0;
  dw=54;
  ny=27;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dw == ny + 27;
  loop invariant fo8 + ny == 27;
  loop invariant ny >= 0;
  loop assigns dw, fo8, ny;
*/
while (ny>0) {
      fo8 += 1;
      dw--;
      ny--;
  }
}