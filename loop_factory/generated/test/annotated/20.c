int main1(int t,int d,int b){
  int kz;
  kz=(b%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == \at(t, Pre) + (((\at(b, Pre) % 20) + 5)) - kz;
  loop invariant d == \at(d, Pre) - (((\at(b, Pre) % 20) + 5) - kz);
  loop invariant kz <= ((\at(b, Pre) % 20) + 5);
  loop invariant t + d == \at(t,Pre) + \at(d,Pre);
  loop invariant kz + t == (\at(b,Pre) % 20) + 5 + \at(t,Pre);
  loop invariant kz + (t - \at(t,Pre)) == ((\at(b,Pre) % 20) + 5);
  loop invariant t + kz == \at(t, Pre) + ((\at(b, Pre) % 20) + 5);
  loop assigns kz, b, t, d;
*/
while (1) {
      if (!(kz>0)) {
          break;
      }
      kz -= 1;
      b = b + kz;
      t += 1;
      d -= 1;
  }
}