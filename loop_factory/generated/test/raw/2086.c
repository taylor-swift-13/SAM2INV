int main1(int q){
  int pv, ho, lg7, x;

  pv=34;
  ho=0;
  lg7=-4;
  x=pv;

  while (ho < pv && x != q) {
      x = x + (x < q ? 1 : -1);
      ho += 1;
      lg7 = lg7+x-x;
  }

}
