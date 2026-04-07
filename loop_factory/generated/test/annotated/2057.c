int main1(){
  int z5ej, f3, f53, rs, cv;
  z5ej=1+14;
  f3=0;
  f53=6;
  rs=10;
  cv=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (z5ej >= f3) || (z5ej == (f3 - 1));
  loop invariant f3 >= 0;
  loop invariant (f53 * rs) == 60;
  loop invariant f3 % 2 == 0;
  loop invariant cv == 2;
  loop invariant f53 >= 6;
  loop invariant ((f53 == 6 && rs == 10 && z5ej >= f3)
                    || (f53 == 6 * cv && rs == 10 / cv && z5ej == f3 - 1));
  loop assigns f3, f53, rs, z5ej;
*/
while (1) {
      if (!(f3++ < z5ej)) {
          break;
      }
      f53 = f53 * cv;
      rs = rs / cv;
      z5ej = f3++;
  }
}