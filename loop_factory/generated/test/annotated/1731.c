int main1(){
  int mga, py, w;
  mga=28;
  py=0;
  w=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= w;
  loop invariant w <= mga;
  loop invariant py == 0;
  loop invariant mga == 28;
  loop assigns w, py;
*/
while (w<mga) {
      w += 1;
      py = (py+1)%3;
      py = py - py;
  }
}