int main1(int n,int p){
  int c, g, v;

  c=p-6;
  g=0;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant c == \at(p, Pre) - 6;
  loop invariant g >= 0;
  loop invariant (g == 0 && v == \at(p, Pre)) || (g >= 1 && v == 0);
  loop invariant (g == 0 ==> v == \at(p, Pre)) && (g != 0 ==> v == 0) && c == \at(p, Pre) - 6 && g >= 0;
  loop invariant p == \at(p, Pre) && n == \at(n, Pre);
  loop invariant v == 0 || v == \at(p, Pre);
  loop invariant c == \at(p, Pre) - 6 && p == \at(p, Pre) && n == \at(n, Pre) && g >= 0;
  loop invariant (g == 0 ==> v == \at(p, Pre)) && (g > 0 ==> v == 0);
  loop invariant (g == 0 && v == \at(p, Pre)) || (g > 0 && v == 0);
  loop invariant p == \at(p, Pre) && n == \at(n, Pre) && c == \at(p, Pre) - 6 && g >= 0;
  loop assigns v, g;
*/
while (1) {
      v = v-v;
      v = v+v;
      g = g+1;
  }

}
