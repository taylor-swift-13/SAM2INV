int main1(){
  int ez, l, t3;

  ez=(1%6)+7;
  l=ez;
  t3=6;

  while (l<ez) {
      t3 = l%5;
      if (l>=t3) {
          t3 = (l-t3)%5;
          t3 = t3+t3-t3;
      }
      else {
          t3 = t3 + t3;
      }
      l = l + 1;
      t3 += l;
  }

}
