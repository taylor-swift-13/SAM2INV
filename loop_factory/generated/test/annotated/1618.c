int main1(int x){
  int sw, y8t, ga, fd7;
  sw=142;
  y8t=0;
  ga=x;
  fd7=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (y8t == sw) ==> (x == 2 * \at(x, Pre) && ga == 2 * \at(x, Pre) + 1 && fd7 == 1 + \at(x, Pre));
  loop invariant y8t == 0 || y8t == sw;
  loop invariant (y8t == 0) ==> (ga == \at(x, Pre) && fd7 == 1 && x == \at(x, Pre));
  loop invariant (0 <= y8t);
  loop invariant (y8t <= sw);
  loop assigns fd7, ga, x, y8t;
*/
while (y8t<sw) {
      fd7 += ga;
      ga = ga + fd7;
      x += x;
      y8t = sw;
  }
}