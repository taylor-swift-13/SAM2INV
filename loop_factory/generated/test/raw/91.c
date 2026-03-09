int main1(int d){
  int o, w, zi1;

  o=d*2;
  w=0;
  zi1=0;

  while (zi1<=o-1) {
      w = (w+1)%8;
      zi1 = zi1 + 1;
      d += zi1;
  }

}
