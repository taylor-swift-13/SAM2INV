int main1(int a){
  int r1, mjhb, kx, siul, tjt, p;
  r1=(a%35)+14;
  mjhb=r1;
  kx=(a%18)+5;
  siul=(a%15)+3;
  tjt=kx;
  p=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (siul - kx) == ((\at(a, Pre) % 15) + 3) - ((\at(a, Pre) % 18) + 5);
  loop invariant tjt == ((\at(a, Pre) % 18) + 5)
                          + (((\at(a, Pre) % 18) + 5) - kx) * ((\at(a, Pre) % 15) + 3)
                          - (((\at(a, Pre) % 18) + 5) - kx) * (((\at(a, Pre) % 18) + 5) - kx + 1) / 2;
  loop invariant kx <= ((a % 18) + 5);
  loop invariant tjt == ((a % 18) + 5)
                       + (((a % 18) + 5) - kx) * (((a % 15) + 3) - 1)
                       - (((( ((a % 18) + 5) - kx) * (((a % 18) + 5) - kx - 1)) / 2));
  loop invariant tjt == ((\at(a, Pre) % 18) + 5) 
                      + (((\at(a, Pre) % 18) + 5) - kx) * ((\at(a, Pre) % 15) + 3)
                      - ((((\at(a, Pre) % 18) + 5) - kx) * (((\at(a, Pre) % 18) + 5) - kx + 1)) / 2;
  loop invariant tjt == (\at(a, Pre) % 18 + 5)
                          + (((\at(a, Pre) % 18 + 5) - kx) * (\at(a, Pre) % 15 + 3))
                          - ((((\at(a, Pre) % 18 + 5) - kx) * (((\at(a, Pre) % 18 + 5) - kx) + 1)) / 2);
  loop invariant 2*tjt == 2*(((a%18) + 5)) +
                          2*(((a%18) + 5) - kx) * (((a%15) + 3) - 1) -
                          (((a%18) + 5) - kx) * (((a%18) + 5) - kx - 1);
  loop assigns kx, siul, tjt;
*/
while (kx!=0) {
      siul -= 1;
      kx = kx - 1;
      tjt = tjt + siul;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p >= 0;
  loop assigns p;
*/
for (; p<=mjhb-1; p++) {
  }
}