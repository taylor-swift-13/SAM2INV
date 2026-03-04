int main1(int n,int w){
  int t;

  t=(w%20)+5;

  while (1) {
      if (!(t>0)) {
          break;
      }
      t = t - 1;
      n += 2;
      w += t;
  }

}
