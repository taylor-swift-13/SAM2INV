int main1(int s){
  int my52, x3, luo, p;
  my52=s;
  x3=0;
  luo=my52;
  p=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (x3 == 0) ==> (p == 1);
  loop invariant (x3 != 0) ==> (p == s);
  loop invariant (luo - my52) >= 0 && ((luo - my52) % 3 == 0) && ((p == 1) || (p == s));
  loop invariant (x3 == 0) || (x3 == my52);
  loop invariant ((x3 == 0 && luo == s && p == 1) ||
                    (x3 == my52 && luo == s + 3 && p == s));
  loop assigns luo, p, x3;
*/
while (x3 < my52) {
      luo = luo + 3;
      p = p * s;
      x3 = my52;
  }
}