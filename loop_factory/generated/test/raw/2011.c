int main1(int f){
  int xx, l2, lf, l;

  xx=f-5;
  l2=0;
  lf=f;
  l=0;

  while (1) {
      if (!(l2 < xx)) {
          break;
      }
      l = l + 2*l2 + 1;
      lf += l;
      l2 += 1;
      lf = lf + 1;
  }

}
