int main1(){
  int zk5, wds, l6x;

  zk5=0;
  wds=(1%28)+10;
  l6x=5;

  while (1) {
      if (!(wds>zk5)) {
          break;
      }
      wds -= zk5;
      zk5 = zk5 + 1;
      l6x = l6x+(wds%7);
  }

}
