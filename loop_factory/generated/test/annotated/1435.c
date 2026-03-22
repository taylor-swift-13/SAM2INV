int main1(){
  int v, ya7b, o3j, w;
  v=(1%12)+6;
  ya7b=v;
  o3j=ya7b;
  w=v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o3j == ya7b;
  loop invariant ya7b == w;
  loop invariant v > 0;
  loop invariant ya7b >= 0;
  loop invariant ya7b <= v;
  loop assigns o3j, w, ya7b;
*/
while (ya7b > 0 && v > 0) {
      o3j -= 1;
      w = w - 1;
      ya7b = ya7b - 1;
  }
}