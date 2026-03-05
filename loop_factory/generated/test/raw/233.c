int main1(int a){
  int s, z6;

  s=59;
  z6=0;

  while (z6<s) {
      z6 = (z6+1)%6;
      z6 += 1;
      a += z6;
  }

}
