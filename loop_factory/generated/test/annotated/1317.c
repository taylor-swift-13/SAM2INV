int main1(){
  int vto, x9x0, g3h;
  vto=0;
  x9x0=(1%28)+10;
  g3h=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vto >= 0;
  loop invariant x9x0 == 11 - vto*(vto - 1) / 2;
  loop invariant g3h % 2 == 0;
  loop assigns x9x0, vto, g3h;
*/
while (x9x0>vto) {
      x9x0 = x9x0 - vto;
      vto = vto + 1;
      g3h = g3h+(vto%8);
      g3h = g3h*2;
  }
}