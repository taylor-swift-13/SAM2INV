int main1(int s){
  int t5v, o4;

  t5v=s;
  o4=0;

  while (o4<t5v) {
      o4 = (o4+1)%4;
      o4++;
      s = s + o4;
  }

}
