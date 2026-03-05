int main178(int t,int v){
  int fz1, o5q, nor, p, zk, l, a0;

  fz1=77;
  o5q=1;
  nor=(v%20)+10;
  p=(v%15)+8;
  zk=0;
  l=-2;
  a0=fz1;

  while (nor>0&&p>0) {
      if (o5q%2==0) {
          nor = nor - 1;
      }
      else {
          p -= 1;
      }
      zk = zk + nor;
      o5q++;
      a0 = a0 + nor;
      l = l+(o5q%2);
  }

}
