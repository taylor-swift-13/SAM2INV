int main1(){
  int wp, t8, p2i3, owya;

  wp=3;
  t8=(1%18)+5;
  p2i3=(1%15)+3;
  owya=t8;

  while (t8!=0) {
      p2i3--;
      t8 -= 1;
      owya += t8;
  }

  for (; owya<wp; owya += 2) {
      p2i3 += owya;
      p2i3 = p2i3;
  }

}
