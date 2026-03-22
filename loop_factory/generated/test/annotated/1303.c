int main1(int x,int y){
  int f, fx, z, o1, cfrt;
  f=0;
  fx=0;
  z=0;
  o1=(y%18)+5;
  cfrt=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == (((\at(y,Pre) % 18) + 5) - o1) * x * x;
  loop invariant fx == (((\at(y,Pre) % 18) + 5) - o1) * y * y;
  loop invariant z == (((\at(y,Pre) % 18) + 5) - o1) * x * y;
  loop invariant cfrt <= 8 * ((((\at(y,Pre) % 18) + 5) - o1));
  loop invariant cfrt >= 0;
  loop invariant cfrt <= 8 * (((y % 18) + 5) - o1);
  loop invariant f == (((y % 18) + 5) - o1) * (x * x);
  loop invariant fx == (((y % 18) + 5) - o1) * (y * y);
  loop invariant z == (((y % 18) + 5) - o1) * (x * y);
  loop invariant o1 <= ((y % 18) + 5);
  loop assigns f, fx, z, o1, cfrt;
*/
while (o1>=1) {
      o1 -= 1;
      f = f+x*x;
      fx = fx+y*y;
      z = z+x*y;
      cfrt = cfrt+(fx%9);
  }
}