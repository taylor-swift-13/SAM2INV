int main1(int b){
  int stn, il, ta5s, l8, man;

  stn=103;
  il=0;
  ta5s=1;
  l8=1;
  man=-1;

  while (ta5s<=stn) {
      il = il + 1;
      l8 += 2;
      man = man+l8+il;
      ta5s += l8;
  }

}
