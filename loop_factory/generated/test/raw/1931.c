int main1(int a){
  int sp, au9, i;

  sp=a+24;
  au9=0;
  i=3;

  while (au9 < sp) {
      i = i + a;
      au9++;
      a = a + au9;
  }

}
