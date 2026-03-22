int main1(){
  int wcm, b7m, um;
  wcm=(1%6)+13;
  b7m=0;
  um=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= b7m;
  loop invariant b7m <= wcm;
  loop invariant (b7m < wcm/2) ==> (um == 6 + 5*b7m);
  loop invariant (b7m >= wcm/2) ==> (um == 6 + 5*b7m + 2*(b7m - wcm/2));
  loop invariant ((b7m <= 6) ==> (um == 6 + 5*b7m)) && ((b7m > 6) ==> (um == 7*b7m - 8));
  loop assigns b7m, um;
*/
while (b7m<wcm) {
      if (!(!(b7m>=wcm/2))) {
          um += 2;
      }
      um = um + 5;
      b7m++;
  }
}