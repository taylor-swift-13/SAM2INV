int main1(){
  int d8ey, vm, gt, h;

  d8ey=(1%14)+14;
  vm=d8ey;
  gt=d8ey;
  h=d8ey;

  while (vm>=1) {
      gt = gt+h+h;
      vm = vm - 1;
  }

}
